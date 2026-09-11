import Vsa.Sim.ClosureParamStage
import Vsa.Sim.ClosureEnvNewResume
import Vsa.Sim.AstReadGeometry
import Vsa.MemReprReadArrays
import Vsa.Sim.RuntimeOwnershipShared

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The closure's names and the evaluated arguments in the caller's actual array. -/
structure FoldData (m : Mem) (N : NativeAddrs) (phiC : Addr → Nat)
    (shared : Nat → Prop) (sp closure names : BitVec 64)
    (params : List String) (values : List Value) : Prop where
  arity : values.length = params.length
  bound : values.length ≤ 32
  namesRead : read64 m (closure.toNat + 16) = some names.toNat
  namesCovered : Covers shared (closure.toNat + 16) 8
  paramsOwned : ParamsReprWithin m shared names.toNat params.length params
  arguments : ∀ i (hi : i < values.length),
    ValueRepr m N phiC (sp.toNat + 240 + 24 * i) values[i]
  owned : ∀ i (hi : i < values.length),
    ValueOwned m shared (sp.toNat + 240 + 24 * i) values[i]

/-- Shared agreement and the argument-array frame preserve all remaining inputs. -/
theorem FoldData.transport
    {m m' : Mem} {N : NativeAddrs} {phiC : Addr → Nat} {shared shared' : Nat → Prop}
    {sp closure names : BitVec 64} {params : List String} {values : List Value}
    (h : FoldData m N phiC shared sp closure names params values)
    (agreement : AgreeP shared m m') (includes : ∀ k, shared k → shared' k)
    (arguments : ∀ k, sp.toNat + 240 ≤ k → k < sp.toNat + 1008 → m[k]? = m'[k]?) :
    FoldData m' N phiC shared' sp closure names params values := by
  let P := fun k => shared k ∨ (sp.toNat + 240 ≤ k ∧ k < sp.toNat + 1008)
  have memory : AgreeP P m m' := by
    intro k hk
    rcases hk with hk | hk
    · exact agreement k hk
    · exact arguments k hk.1 hk.2
  have header (i : Nat) (hi : i < values.length) :
      ∀ k, valHeader (sp.toNat + 240 + 24 * i) k → P k := by
    intro k hk
    right
    change sp.toNat + 240 + 24 * i ≤ k ∧ k < sp.toNat + 240 + 24 * i + 24 at hk
    have := h.bound
    omega
  exact
    { arity := h.arity, bound := h.bound
      namesRead := (h.namesCovered.read64_eq agreement).symm.trans h.namesRead
      namesCovered := h.namesCovered.mono includes
      paramsOwned := h.paramsOwned.map agreement includes
      arguments := fun i hi => valueRepr_agreeP memory (header i hi)
        ((h.owned i hi).covered (fun k hk => Or.inl hk)) (h.arguments i hi)
      owned := fun i hi => ((h.owned i hi).transport memory (header i hi)
        (fun _ hk => Or.inl hk)).mono includes }

/-- The selected parameter read, argument, and name ownership at the actual loop head. -/
structure SelectedInput (N : NativeAddrs) (phiC : Addr → Nat) (shared : Nat → Prop)
    (sp cursor index scope closure names name : BitVec 64) (param : String) (value : Value)
    (before : Config) : Prop where
  pre : Pre sp cursor index scope closure names name before
  argument : ValueRepr before.σ.mem N phiC cursor.toNat value
  owned : ValueOwned before.σ.mem shared cursor.toNat value
  name : SharedCString before.σ.mem shared name.toNat param

/-- Ownership of the real pointer array supplies the next reflected staging span. -/
theorem FoldData.select
    {N : NativeAddrs} {phiC : Addr → Nat} {shared : Nat → Prop}
    {sp scope closure names : BitVec 64} {params : List String} {values : List Value}
    {before : Config} {SL : StackLayout} {alloc : Allocations}
    (h : FoldData before.σ.mem N phiC shared sp closure names params values)
    (immutable : Immutable alloc shared InitialReadableByte (InitialWriteByte SL))
    (geometry : ClosureEnvNewResume.Geometry sp)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (codeOff : sp.toNat + 88 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sp.toNat)
    (i : Nat) (hi : i < values.length)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x800032dc#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (regs : GHolds before.σ (callClosureFoldStageL sp
      (BitVec.ofNat 64 (sp.toNat + 240 + 24 * i)) (BitVec.ofNat 64 (8 * i)) scope closure))
    (code : Code.Eval_exprLoaded before.σ.mem) :
    ∃ name, SelectedInput N phiC shared sp (BitVec.ofNat 64 (sp.toNat + 240 + 24 * i))
      (BitVec.ofNat 64 (8 * i)) scope closure names name (params[i]'(by have := h.arity; omega)) values[i] before := by
  obtain ⟨p, cell⟩ := h.paramsOwned.pointers.get i (by have := h.arity; omega)
  have cellGeom := AstReadGeometry.of_covered immutable cell.covered (by decide)
  have closureGeom := AstReadGeometry.of_covered immutable h.namesCovered (by decide)
  have cellHi : names.toNat + 8 * i + 8 ≤ 0x100000000 := cellGeom.ram_hi
  have cellOff := cellGeom.stack_disjoint (by omega)
  have argNat : (BitVec.ofNat 64 (sp.toNat + 240 + 24 * i)).toNat =
      sp.toNat + 240 + 24 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := geometry.hi; have := h.bound; omega)]
  have cellNat : (names + BitVec.ofNat 64 (8 * i)).toNat = names.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8 * i < 2^64 by have := h.bound; omega),
      Nat.mod_eq_of_lt (show names.toNat + 8 * i < 2^64 by omega)]
  have nameNat : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ cell.read)]
  have access : Geometry before.σ.mem sp (BitVec.ofNat 64 (sp.toNat + 240 + 24 * i))
      closure (names + BitVec.ofNat 64 (8 * i)) := by
    refine
    { stack := ⟨geometry.lo, by have := geometry.hi; omega, geometry.htif, geometry.align⟩
      sourceLo := ?_, sourceHi := ?_, sourceHtif := ?_, sourceAfter := ?_
      closureLo := closureGeom.ram_lo, closureHi := by have := closureGeom.ram_hi; omega
      closureHtif := by have := closureGeom.htif; omega
      cellLo := ?_, cellHi := ?_, cellHtif := ?_, cellOff := ?_, codeOff := codeOff }
    · rw [argNat]; have := geometry.lo; omega
    · rw [argNat]; have := geometry.hi; have := h.bound; omega
    · rw [argNat]; have := geometry.htif; omega
    · rw [argNat]; omega
    · rw [cellNat]; exact cellGeom.ram_lo
    · rw [cellNat]; exact cellGeom.ram_hi
    · rw [cellNat]; have := cellGeom.htif; omega
    · rw [cellNat]; omega
  have pre : Pre sp (BitVec.ofNat 64 (sp.toNat + 240 + 24 * i))
      (BitVec.ofNat 64 (8 * i)) scope closure names (BitVec.ofNat 64 p) before :=
    { good := good, tick := tick, pc := pc, minstret := minstret, regs := regs
      geometry := access, namesRead := h.namesRead
      nameRead := by rw [cellNat, nameNat]; exact cell.read
      code := code }
  refine ⟨BitVec.ofNat 64 p,
    { pre := pre
      argument := by rw [argNat]; exact h.arguments i hi
      owned := by rw [argNat]; exact h.owned i hi
      name := by rw [nameNat]; exact ⟨cell.target.1, cell.target.2⟩ }⟩

end Vsa.Sim.ClosureParam
