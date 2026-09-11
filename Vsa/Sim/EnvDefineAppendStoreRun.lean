import Vsa.Sim.rows.EnvDefineAppendLane
import Vsa.Sim.SegEffect

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Memory and live registers at the actual return from the name copy. -/
structure EnvDefineAppendStoreInput
    (saved : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (env src copied sp : BitVec 64) (parent : Option Addr) (vars : List (String × Value))
    (name : String) (v : Value) (cap names vals : Nat) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80002b44#64
  spReg : before.σ.regs.get? Register.x2 = some sp
  regs : GHolds before.σ (appendStoreL env src copied)
  savedSpills : EnvDefineSavedSpillFrame sp saved before
  code : Code.Env_defineLoaded before.σ.mem
  frame : FrameRepr before.σ.mem N phiF phiC env.toNat ⟨parent, vars⟩
  capRead : read32 before.σ.mem (env.toNat + 4) = some cap
  namesRead : read64 before.σ.mem (env.toNat + 8) = some names
  valuesRead : read64 before.σ.mem (env.toNat + 16) = some vals
  room : vars.length < cap
  word : ValueWordRepr before.σ.mem N phiC src.toNat v
  copiedName : CString before.σ.mem copied.toNat name
  footprint : EnvDefineAppendFootprint before.σ.mem env.toNat names vals vars.length
    copied.toNat src.toNat vars name v
  geometry : AppendStoreFactsGeom env src vars.length names vals
  namesArena : A.contains (names + 8 * vars.length) 8
  valuesArena : A.contains (vals + 24 * vars.length) 24
  countArena : A.contains env.toNat 4
  arenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo
  arenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo

/-- Memory effects retained through the append stores and their epilogue. -/
structure EnvDefineAppendMemory
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (env src copied sp : BitVec 64) (parent : Option Addr) (vars : List (String × Value))
    (name : String) (v : Value) (cap names vals : Nat) (before after : Config) : Prop where
  readback : EnvDefineAppendReadback after.σ.mem N phiF phiC env.toNat parent vars name v cap names vals
  word : ValueWordRepr after.σ.mem N phiC (vals + 24 * vars.length) v
  copy : ∀ k, k < 24 → after.σ.mem[vals + 24 * vars.length + k]? =
    some ((before.σ.mem[src.toNat + k]?).getD 0)
  nameRead : read64 after.σ.mem (names + 8 * vars.length) = some copied.toNat
  nameString : CString after.σ.mem copied.toNat name
  agreement : AgreeP (AppendUntouched env.toNat names vals vars.length) before.σ.mem after.σ.mem
  outsideArena : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem

/-- Exact append stores, with the copied value and caller frame retained. -/
structure EnvDefineAppendStored
    (saved : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (env src copied sp : BitVec 64) (parent : Option Addr) (vars : List (String × Value))
    (name : String) (v : Value) (cap names vals : Nat) (before after : Config) extends
    EnvDefineAppendMemory N A phiF phiC env src copied sp parent vars name v cap names vals before after : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80002aec#64
  spReg : after.σ.regs.get? Register.x2 = some sp
  resultReg : ∃ w, after.σ.regs.get? Register.x10 = some w
  savedSpills : EnvDefineSavedSpillFrame sp saved after
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Run the existing five-store segment and retain its readback and full caller frame. -/
theorem EnvDefineAppendStoreInput.run
    {saved : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {env src copied sp : BitVec 64} {parent : Option Addr} {vars : List (String × Value)}
    {name : String} {v : Value} {cap names vals : Nat} {before : Config}
    (h : EnvDefineAppendStoreInput saved N A phiF phiC env src copied sp parent vars
      name v cap names vals before) :
    ∃ after, Steps before after ∧
      EnvDefineAppendStored saved N A phiF phiC env src copied sp parent vars
        name v cap names vals before after := by
  obtain ⟨lds, facts, countWord, namesWord, valuesWord, p0, p1, p2⟩ :=
    appendStoreFacts env src copied vars.length names vals before.σ.mem N phiC v h.code
      h.frame.1 h.namesRead h.valuesRead h.word h.geometry
  have count32 := h.geometry.countNext32
  have namesHi : names + 8 * vars.length + 8 ≤ 2^64 := by have := h.geometry.nameHi; omega
  have valuesHi : vals + 24 * vars.length + 24 ≤ 2^64 := by have := h.geometry.valsHi; omega
  have envHi : env.toNat + 4 ≤ 2^64 := by have := h.geometry.envHi; omega
  have writes := appendStoreWritesInArena A env src copied lds vars.length names vals
    countWord namesWord valuesWord count32 namesHi valuesHi envHi h.namesArena h.valuesArena h.countArena
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed appendStoreSeg (appendStoreL env src copied) lds
    0x80002b44#64 vm (fun k => A.lo ≤ k ∧ k < A.hi) AbiPreserved
    [(10, bytesVal .ld (lds.getD 4 []))] before h.good h.pc hvm h.regs
    (by change KeysOK [20, 21, 9]; decide) facts
    (by change ChainOK 0x80002b44#64 [20, 21, 9] appendStoreSeg; decide) h.tick
    (by
      intro k outside
      apply Eq.symm
      apply writeLog_getElem_disjoint k _ before.σ.mem (appendStoreLogWidths env src copied lds)
      intro e he
      obtain ⟨lo, hi⟩ := writes e he
      omega)
    abiPreserved_noise (by decide) (by
      simp [GProjects, appendStoreSeg, evalBlocks, evalBlock, SegEvalState.init,
        runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG,
        appendStoreL, mkLine, decodeM, List.getD_eq_getElem?_getD])
  have memory : after.σ.mem = AppendStoreTower before.σ.mem env.toNat names vals vars.length copied
      (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 [])) (bytesVal .ld (lds.getD 5 [])) := by
    rw [C.mem, appendStoreLogExact env src copied lds vars.length names vals
      countWord namesWord valuesWord count32 namesHi valuesHi envHi]
    rfl
  have agreement : AgreeP (AppendUntouched env.toNat names vals vars.length) before.σ.mem after.σ.mem := by
    rw [memory]; exact appendStoreTowerAgree _ _ _ _ _ _ _ _ _
  have copy : ∀ k, k < 24 → after.σ.mem[vals + 24 * vars.length + k]? =
      some ((before.σ.mem[src.toNat + k]?).getD 0) := by
    rw [memory]
    exact appendStoreTowerCopy _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl p0 p1 p2 h.footprint.valueCount
  have readback : EnvDefineAppendReadback after.σ.mem N phiF phiC env.toNat parent vars name v cap names vals := by
    rw [C.mem]
    exact appendStoreReadback env src copied lds before.σ.mem N phiF phiC parent vars name v cap names vals
      h.frame h.capRead h.room h.namesRead h.valuesRead countWord namesWord valuesWord p0 p1 p2
      h.word h.copiedName h.footprint count32 namesHi valuesHi envHi
  have total : ValueWordsTotal after.σ.mem (vals + 24 * vars.length) := by
    obtain ⟨d0, d1, d2, r0, r1, r2⟩ := h.word.total
    exact ⟨d0, d1, d2, by simpa using read64_copy_total copy (by decide : 0 + 8 ≤ 24) r0,
      read64_copy_total copy (by decide : 8 + 8 ≤ 24) r1,
      read64_copy_total copy (by decide : 16 + 8 ≤ 24) r2⟩
  have publicFrame := appendStorePublicFrame_of_arena A sp env src copied lds before.σ.mem
    writes h.arenaStack h.arenaCode
  refine ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := C.pc
      spReg := (C.reg_frame _ (by decide)).trans h.spReg
      resultReg := ⟨_, C.selected_regs.1⟩
      savedSpills := ?_, readback := readback, word := ⟨readback.newValue, total⟩
      copy := copy, nameRead := ?_
      nameString := cstring_agreeP agreement h.copiedName h.footprint.copiedString
      agreement := agreement, outsideArena := C.outside, presence := ?_
      output := C.output, frame := C.reg_frame }⟩
  · rw [memory]
    unfold AppendStoreTower
    rw [read64_writeMap4_disjoint _ _ _ _ h.footprint.newNameCount,
      read64_writeMap8_disjoint _ _ _ _ (by rcases h.footprint.newNameValue with h | h <;> omega),
      read64_writeMap8_disjoint _ _ _ _ (by rcases h.footprint.newNameValue with h | h <;> omega),
      read64_writeMap8_disjoint _ _ _ _ (by rcases h.footprint.newNameValue with h | h <;> omega),
      read64_writeMap8, sdData_toNat]
  · rw [C.mem]; exact memExtends_writeLog _ _
  · apply h.savedSpills.of_interval_agree
    · intro k lo hi; rw [C.mem]; exact publicFrame.code k lo hi
    · intro k lo hi; rw [C.mem]; exact publicFrame.spills k lo hi

#print axioms EnvDefineAppendStoreInput.run

end Vsa.Sim
